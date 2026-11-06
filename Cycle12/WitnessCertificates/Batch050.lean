import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs050

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch050

def certificate1000 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs050.envelope1000,(47/20),(63/200),(3518599610248635872887/125000000000000000),(373920137/200000000),32,(1007/1000),(188079915215381929/500000000000000000),1,(4472588439023811/1000000000000000000)⟩
theorem valid1000 : certificate1000.Valid := by
  refine ⟨MajorityCertificates.Inputs050.inputs_valid1000,?_⟩
  decide +kernel
theorem sound1000 : certificate1000.Sound :=
  rat_witness_certificate_sound certificate1000 valid1000 MajorityCertificates.Inputs050.envelope_sound1000

def certificate1001 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs050.envelope1001,(47/20),(3757/20000),(27699124992646009937571/1000000000000000000),(381925337/200000000),32,(247574443/500000000),0,1,(172233501524381/1000000000000000000)⟩
theorem valid1001 : certificate1001.Valid := by
  refine ⟨MajorityCertificates.Inputs050.inputs_valid1001,?_⟩
  decide +kernel
theorem sound1001 : certificate1001.Sound :=
  rat_witness_certificate_sound certificate1001 valid1001 MajorityCertificates.Inputs050.envelope_sound1001

def certificate1002 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs050.envelope1002,(47/20),(3757/20000),(27699124992646009937571/1000000000000000000),(69813837/40000000),32,(1518993843/1000000000),0,(225010370159317719/200000000000000000),(79582775362553/200000000000000000)⟩
theorem valid1002 : certificate1002.Valid := by
  refine ⟨MajorityCertificates.Inputs050.inputs_valid1002,?_⟩
  decide +kernel
theorem sound1002 : certificate1002.Sound :=
  rat_witness_certificate_sound certificate1002 valid1002 MajorityCertificates.Inputs050.envelope_sound1002

def certificate1003 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs050.envelope1003,(47/20),(63/200),(27699124992646009937571/1000000000000000000),(1873712237/1000000000),32,(1007/1000),(187893810283559447/500000000000000000),1,(447258843902381/100000000000000000)⟩
theorem valid1003 : certificate1003.Valid := by
  refine ⟨MajorityCertificates.Inputs050.inputs_valid1003,?_⟩
  decide +kernel
theorem sound1003 : certificate1003.Sound :=
  rat_witness_certificate_sound certificate1003 valid1003 MajorityCertificates.Inputs050.envelope_sound1003

def certificate1004 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs050.envelope1004,(47/20),(1883/10000),(26698485819870823135647/1000000000000000000),(1910484869/1000000000),32,(496382657/1000000000),0,1,(179403549420059/1000000000000000000)⟩
theorem valid1004 : certificate1004.Valid := by
  refine ⟨MajorityCertificates.Inputs050.inputs_valid1004,?_⟩
  decide +kernel
theorem sound1004 : certificate1004.Sound :=
  rat_witness_certificate_sound certificate1004 valid1004 MajorityCertificates.Inputs050.envelope_sound1004

def certificate1005 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs050.envelope1005,(47/20),(1883/10000),(26698485819870823135647/1000000000000000000),(1743833457/1000000000),32,(380146809/250000000),0,(281263448549432469/250000000000000000),(415683727652471/1000000000000000000)⟩
theorem valid1005 : certificate1005.Valid := by
  refine ⟨MajorityCertificates.Inputs050.inputs_valid1005,?_⟩
  decide +kernel
theorem sound1005 : certificate1005.Sound :=
  rat_witness_certificate_sound certificate1005 valid1005 MajorityCertificates.Inputs050.envelope_sound1005

def certificate1006 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs050.envelope1006,(47/20),(63/200),(26698485819870823135647/1000000000000000000),(234539337/125000000),32,(1007/1000),(46944269038172227/125000000000000000),1,(4472588439023811/1000000000000000000)⟩
theorem valid1006 : certificate1006.Valid := by
  refine ⟨MajorityCertificates.Inputs050.inputs_valid1006,?_⟩
  decide +kernel
theorem sound1006 : certificate1006.Sound :=
  rat_witness_certificate_sound certificate1006 valid1006 MajorityCertificates.Inputs050.envelope_sound1006

def certificate1007 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs050.envelope1007,(47/20),(473/2500),(5179120136195503627223/200000000000000000),(1914068153/1000000000),32,(498664371/1000000000),0,1,(92621757673993/500000000000000000)⟩
theorem valid1007 : certificate1007.Valid := by
  refine ⟨MajorityCertificates.Inputs050.inputs_valid1007,?_⟩
  decide +kernel
theorem sound1007 : certificate1007.Sound :=
  rat_witness_certificate_sound certificate1007 valid1007 MajorityCertificates.Inputs050.envelope_sound1007

def certificate1008 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs050.envelope1008,(47/20),(473/2500),(5179120136195503627223/200000000000000000),(871245609/500000000),32,(1521365253/1000000000),0,(562527731067123583/500000000000000000),(433360438559531/1000000000000000000)⟩
theorem valid1008 : certificate1008.Valid := by
  refine ⟨MajorityCertificates.Inputs050.inputs_valid1008,?_⟩
  decide +kernel
theorem sound1008 : certificate1008.Sound :=
  rat_witness_certificate_sound certificate1008 valid1008 MajorityCertificates.Inputs050.envelope_sound1008

def certificate1009 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs050.envelope1009,(47/20),(63/200),(5179120136195503627223/200000000000000000),(1884538681/1000000000),32,(1007/1000),(187412143365877869/500000000000000000),1,(4472588439023811/1000000000000000000)⟩
theorem valid1009 : certificate1009.Valid := by
  refine ⟨MajorityCertificates.Inputs050.inputs_valid1009,?_⟩
  decide +kernel
theorem sound1009 : certificate1009.Sound :=
  rat_witness_certificate_sound certificate1009 valid1009 MajorityCertificates.Inputs050.envelope_sound1009

def certificate1010 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs050.envelope1010,(47/20),(1901/10000),(12570243598073477431933/500000000000000000),(1917690327/1000000000),32,(500948441/1000000000),0,1,(95561121607587/500000000000000000)⟩
theorem valid1010 : certificate1010.Valid := by
  refine ⟨MajorityCertificates.Inputs050.inputs_valid1010,?_⟩
  decide +kernel
theorem sound1010 : certificate1010.Sound :=
  rat_witness_certificate_sound certificate1010 valid1010 MajorityCertificates.Inputs050.envelope_sound1010

def certificate1011 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs050.envelope1011,(47/20),(1901/10000),(12570243598073477431933/500000000000000000),(174110349/100000000),32,(1522208957/1000000000),0,(1125057128047052597/1000000000000000000),(28204788668019/62500000000000000)⟩
theorem valid1011 : certificate1011.Valid := by
  refine ⟨MajorityCertificates.Inputs050.inputs_valid1011,?_⟩
  decide +kernel
theorem sound1011 : certificate1011.Sound :=
  rat_witness_certificate_sound certificate1011 valid1011 MajorityCertificates.Inputs050.envelope_sound1011

def certificate1012 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs050.envelope1012,(47/20),(63/200),(12570243598073477431933/500000000000000000),(473191971/250000000),32,(1007/1000),(2992859428952421/8000000000000000),1,(1118147109755953/250000000000000000)⟩
theorem valid1012 : certificate1012.Valid := by
  refine ⟨MajorityCertificates.Inputs050.inputs_valid1012,?_⟩
  decide +kernel
theorem sound1012 : certificate1012.Sound :=
  rat_witness_certificate_sound certificate1012 valid1012 MajorityCertificates.Inputs050.envelope_sound1012

def certificate1013 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs050.envelope1013,(47/20),(47/250),(48859186672234238561/2000000000000000),(38433897/20000000),32,(98894161/200000000),0,1,(367525809166807/1000000000000000000)⟩
theorem valid1013 : certificate1013.Valid := by
  refine ⟨MajorityCertificates.Inputs050.inputs_valid1013,?_⟩
  decide +kernel
theorem sound1013 : certificate1013.Sound :=
  rat_witness_certificate_sound certificate1013 valid1013 MajorityCertificates.Inputs050.envelope_sound1013

def certificate1014 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs050.envelope1014,(47/20),(47/250),(48859186672234238561/2000000000000000),(1740393767/1000000000),32,(305240323/200000000),0,(281264697630926367/250000000000000000),(554816252781031/1000000000000000000)⟩
theorem valid1014 : certificate1014.Valid := by
  refine ⟨MajorityCertificates.Inputs050.inputs_valid1014,?_⟩
  decide +kernel
theorem sound1014 : certificate1014.Sound :=
  rat_witness_certificate_sound certificate1014 valid1014 MajorityCertificates.Inputs050.envelope_sound1014

def certificate1015 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs050.envelope1015,(47/20),(63/200),(48859186672234238561/2000000000000000),(951353857/500000000),32,(503501233/500000000),(373259989765724541/1000000000000000000),1,(4475020268216611/1000000000000000000)⟩
theorem valid1015 : certificate1015.Valid := by
  refine ⟨MajorityCertificates.Inputs050.inputs_valid1015,?_⟩
  decide +kernel
theorem sound1015 : certificate1015.Sound :=
  rat_witness_certificate_sound certificate1015 valid1015 MajorityCertificates.Inputs050.envelope_sound1015

def certificate1016 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs050.envelope1016,(47/20),(1919/10000),(11879850903099233585143/500000000000000000),(385007843/200000000),32,(252762549/500000000),0,1,(101436726393161/500000000000000000)⟩
theorem valid1016 : certificate1016.Valid := by
  refine ⟨MajorityCertificates.Inputs050.inputs_valid1016,?_⟩
  decide +kernel
theorem sound1016 : certificate1016.Sound :=
  rat_witness_certificate_sound certificate1016 valid1016 MajorityCertificates.Inputs050.envelope_sound1016

def certificate1017 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs050.envelope1017,(47/20),(1919/10000),(11879850903099233585143/500000000000000000),(1738172843/1000000000),32,(152411791/100000000),0,(112506044815897627/100000000000000000),(244225175087513/500000000000000000)⟩
theorem valid1017 : certificate1017.Valid := by
  refine ⟨MajorityCertificates.Inputs050.inputs_valid1017,?_⟩
  decide +kernel
theorem sound1017 : certificate1017.Sound :=
  rat_witness_certificate_sound certificate1017 valid1017 MajorityCertificates.Inputs050.envelope_sound1017

def certificate1018 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs050.envelope1018,(47/20),(63/200),(11879850903099233585143/500000000000000000),(190937369/100000000),32,(1007/1000),(46587607523382097/125000000000000000),1,(447258843902381/100000000000000000)⟩
theorem valid1018 : certificate1018.Valid := by
  refine ⟨MajorityCertificates.Inputs050.inputs_valid1018,?_⟩
  decide +kernel
theorem sound1018 : certificate1018.Sound :=
  rat_witness_certificate_sound certificate1018 valid1018 MajorityCertificates.Inputs050.envelope_sound1018

def certificate1019 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs050.envelope1019,(47/20),(241/1250),(23127892970843726925201/1000000000000000000),(964381999/500000000),32,(507818031/1000000000),0,1,(521984893677/2500000000000000)⟩
theorem valid1019 : certificate1019.Valid := by
  refine ⟨MajorityCertificates.Inputs050.inputs_valid1019,?_⟩
  decide +kernel
theorem sound1019 : certificate1019.Sound :=
  rat_witness_certificate_sound certificate1019 valid1019 MajorityCertificates.Inputs050.envelope_sound1019

def certificates : List RatWitnessCertificate := [certificate1000,certificate1001,certificate1002,certificate1003,certificate1004,certificate1005,certificate1006,certificate1007,certificate1008,certificate1009,certificate1010,certificate1011,certificate1012,certificate1013,certificate1014,certificate1015,certificate1016,certificate1017,certificate1018,certificate1019]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1000,List.forall_mem_cons.mpr ⟨sound1001,List.forall_mem_cons.mpr ⟨sound1002,List.forall_mem_cons.mpr ⟨sound1003,List.forall_mem_cons.mpr ⟨sound1004,List.forall_mem_cons.mpr ⟨sound1005,List.forall_mem_cons.mpr ⟨sound1006,List.forall_mem_cons.mpr ⟨sound1007,List.forall_mem_cons.mpr ⟨sound1008,List.forall_mem_cons.mpr ⟨sound1009,List.forall_mem_cons.mpr ⟨sound1010,List.forall_mem_cons.mpr ⟨sound1011,List.forall_mem_cons.mpr ⟨sound1012,List.forall_mem_cons.mpr ⟨sound1013,List.forall_mem_cons.mpr ⟨sound1014,List.forall_mem_cons.mpr ⟨sound1015,List.forall_mem_cons.mpr ⟨sound1016,List.forall_mem_cons.mpr ⟨sound1017,List.forall_mem_cons.mpr ⟨sound1018,List.forall_mem_cons.mpr ⟨sound1019,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch050
