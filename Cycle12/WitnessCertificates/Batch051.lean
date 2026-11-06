import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs051

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch051

def certificate1020 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs051.envelope1020,(47/20),(241/1250),(23127892970843726925201/1000000000000000000),(1736616351/1000000000),32,(1525199999/1000000000),0,(562531049777718479/500000000000000000),(101510255466029/200000000000000000)⟩
theorem valid1020 : certificate1020.Valid := by
  refine ⟨MajorityCertificates.Inputs051.inputs_valid1020,?_⟩
  decide +kernel
theorem sound1020 : certificate1020.Sound :=
  rat_witness_certificate_sound certificate1020 valid1020 MajorityCertificates.Inputs051.envelope_sound1020

def certificate1021 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs051.envelope1021,(47/20),(63/200),(23127892970843726925201/1000000000000000000),(1917719/1000000),32,(1007/1000),(372013663676214123/1000000000000000000),1,(447258843902381/100000000000000000)⟩
theorem valid1021 : certificate1021.Valid := by
  refine ⟨MajorityCertificates.Inputs051.inputs_valid1021,?_⟩
  decide +kernel
theorem sound1021 : certificate1021.Sound :=
  rat_witness_certificate_sound certificate1021 valid1021 MajorityCertificates.Inputs051.envelope_sound1021

def certificate1022 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs051.envelope1022,(47/20),(1937/10000),(5632878126100667510879/250000000000000000),(1932526043/1000000000),32,(408091/800000),0,1,(107346057372917/500000000000000000)⟩
theorem valid1022 : certificate1022.Valid := by
  refine ⟨MajorityCertificates.Inputs051.inputs_valid1022,?_⟩
  decide +kernel
theorem sound1022 : certificate1022.Sound :=
  rat_witness_certificate_sound certificate1022 valid1022 MajorityCertificates.Inputs051.envelope_sound1022

def certificate1023 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs051.envelope1023,(47/20),(1937/10000),(5632878126100667510879/250000000000000000),(1734983107/1000000000),32,(1526387467/1000000000),0,(140632967915511117/125000000000000000),(6588139801749/12500000000000000)⟩
theorem valid1023 : certificate1023.Valid := by
  refine ⟨MajorityCertificates.Inputs051.inputs_valid1023,?_⟩
  decide +kernel
theorem sound1023 : certificate1023.Sound :=
  rat_witness_certificate_sound certificate1023 valid1023 MajorityCertificates.Inputs051.envelope_sound1023

def certificate1024 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs051.envelope1024,(47/20),(63/200),(5632878126100667510879/250000000000000000),(963051587/500000000),32,(1007/1000),(185668092479471389/500000000000000000),1,(447258843902381/100000000000000000)⟩
theorem valid1024 : certificate1024.Valid := by
  refine ⟨MajorityCertificates.Inputs051.inputs_valid1024,?_⟩
  decide +kernel
theorem sound1024 : certificate1024.Sound :=
  rat_witness_certificate_sound certificate1024 valid1024 MajorityCertificates.Inputs051.envelope_sound1024

def certificate1025 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs051.envelope1025,(47/20),(973/5000),(2196814309103604449509/100000000000000000),(1936379263/1000000000),32,(20496289/40000000),0,1,(11032039667019/50000000000000000)⟩
theorem valid1025 : certificate1025.Valid := by
  refine ⟨MajorityCertificates.Inputs051.inputs_valid1025,?_⟩
  decide +kernel
theorem sound1025 : certificate1025.Sound :=
  rat_witness_certificate_sound certificate1025 valid1025 MajorityCertificates.Inputs051.envelope_sound1025

def certificate1026 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs051.envelope1026,(47/20),(973/5000),(2196814309103604449509/100000000000000000),(86669411/50000000),32,(763768891/500000000),0,(1125065378085029097/1000000000000000000),(68350914721877/125000000000000000)⟩
theorem valid1026 : certificate1026.Valid := by
  refine ⟨MajorityCertificates.Inputs051.inputs_valid1026,?_⟩
  decide +kernel
theorem sound1026 : certificate1026.Sound :=
  rat_witness_certificate_sound certificate1026 valid1026 MajorityCertificates.Inputs051.envelope_sound1026

def certificate1027 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs051.envelope1027,(47/20),(63/200),(2196814309103604449509/100000000000000000),(1934529049/1000000000),32,(1007/1000),(185334065075064027/500000000000000000),1,(447258843902381/100000000000000000)⟩
theorem valid1027 : certificate1027.Valid := by
  refine ⟨MajorityCertificates.Inputs051.inputs_valid1027,?_⟩
  decide +kernel
theorem sound1027 : certificate1027.Sound :=
  rat_witness_certificate_sound certificate1027 valid1027 MajorityCertificates.Inputs051.envelope_sound1027

def certificate1028 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs051.envelope1028,(47/20),(77/400),(10717789802044865406831/500000000000000000),(975866373/500000000),32,(504790141/1000000000),0,1,(942125216409/3906250000000000)⟩
theorem valid1028 : certificate1028.Valid := by
  refine ⟨MajorityCertificates.Inputs051.inputs_valid1028,?_⟩
  decide +kernel
theorem sound1028 : certificate1028.Sound :=
  rat_witness_certificate_sound certificate1028 valid1028 MajorityCertificates.Inputs051.envelope_sound1028

def certificate1029 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs051.envelope1029,(47/20),(77/400),(10717789802044865406831/500000000000000000),(346145949/200000000),32,(767014387/500000000),0,(1125067002468154103/1000000000000000000),(71234220270337/100000000000000000)⟩
theorem valid1029 : certificate1029.Valid := by
  refine ⟨MajorityCertificates.Inputs051.inputs_valid1029,?_⟩
  decide +kernel
theorem sound1029 : certificate1029.Sound :=
  rat_witness_certificate_sound certificate1029 valid1029 MajorityCertificates.Inputs051.envelope_sound1029

def certificate1030 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs051.envelope1030,(47/20),(63/200),(10717789802044865406831/500000000000000000),(388446811/200000000),32,(50350041/50000000),(370068583177473717/1000000000000000000),1,(4473397077790059/1000000000000000000)⟩
theorem valid1030 : certificate1030.Valid := by
  refine ⟨MajorityCertificates.Inputs051.inputs_valid1030,?_⟩
  decide +kernel
theorem sound1030 : certificate1030.Sound :=
  rat_witness_certificate_sound certificate1030 valid1030 MajorityCertificates.Inputs051.envelope_sound1030

def certificate1031 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs051.envelope1031,(47/20),(491/2500),(10465903641982879244853/500000000000000000),(1944081063/1000000000),32,(103402831/200000000),0,1,(907534732887/3906250000000000)⟩
theorem valid1031 : certificate1031.Valid := by
  refine ⟨MajorityCertificates.Inputs051.inputs_valid1031,?_⟩
  decide +kernel
theorem sound1031 : certificate1031.Sound :=
  rat_witness_certificate_sound certificate1031 valid1031 MajorityCertificates.Inputs051.envelope_sound1031

def certificate1032 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs051.envelope1032,(47/20),(491/2500),(10465903641982879244853/500000000000000000),(865260307/500000000),32,(1529467921/1000000000),0,(281267153778475739/250000000000000000),(588008671869457/1000000000000000000)⟩
theorem valid1032 : certificate1032.Valid := by
  refine ⟨MajorityCertificates.Inputs051.inputs_valid1032,?_⟩
  decide +kernel
theorem sound1032 : certificate1032.Sound :=
  rat_witness_certificate_sound certificate1032 valid1032 MajorityCertificates.Inputs051.envelope_sound1032

def certificate1033 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs051.envelope1033,(47/20),(63/200),(10465903641982879244853/500000000000000000),(975751743/500000000),32,(503500001/500000000),(369360236706184483/1000000000000000000),1,(4472590411315087/1000000000000000000)⟩
theorem valid1033 : certificate1033.Valid := by
  refine ⟨MajorityCertificates.Inputs051.inputs_valid1033,?_⟩
  decide +kernel
theorem sound1033 : certificate1033.Sound :=
  rat_witness_certificate_sound certificate1033 valid1033 MajorityCertificates.Inputs051.envelope_sound1033

def certificate1034 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs051.envelope1034,(47/20),(1973/10000),(818199300286210727751/40000000000000000),(1947990803/1000000000),32,(32457621/62500000),0,1,(47630171990641/200000000000000000)⟩
theorem valid1034 : certificate1034.Valid := by
  refine ⟨MajorityCertificates.Inputs051.inputs_valid1034,?_⟩
  decide +kernel
theorem sound1034 : certificate1034.Sound :=
  rat_witness_certificate_sound certificate1034 valid1034 MajorityCertificates.Inputs051.envelope_sound1034

def certificate1035 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs051.envelope1035,(47/20),(1973/10000),(818199300286210727751/40000000000000000),(1728048847/1000000000),32,(765872041/500000000),0,(35158444208563679/31250000000000000),(608664244525549/1000000000000000000)⟩
theorem valid1035 : certificate1035.Valid := by
  refine ⟨MajorityCertificates.Inputs051.inputs_valid1035,?_⟩
  decide +kernel
theorem sound1035 : certificate1035.Sound :=
  rat_witness_certificate_sound certificate1035 valid1035 MajorityCertificates.Inputs051.envelope_sound1035

def certificate1036 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs051.envelope1036,(47/20),(63/200),(818199300286210727751/40000000000000000),(980033401/500000000),32,(1007/1000),(368719172041113687/1000000000000000000),1,(4472588439023811/1000000000000000000)⟩
theorem valid1036 : certificate1036.Valid := by
  refine ⟨MajorityCertificates.Inputs051.inputs_valid1036,?_⟩
  decide +kernel
theorem sound1036 : certificate1036.Sound :=
  rat_witness_certificate_sound certificate1036 valid1036 MajorityCertificates.Inputs051.envelope_sound1036

def certificate1037 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs051.envelope1037,(47/20),(991/5000),(2500426975050413791941/125000000000000000),(1951950519/1000000000),32,(260815847/500000000),0,1,(121963064493177/500000000000000000)⟩
theorem valid1037 : certificate1037.Valid := by
  refine ⟨MajorityCertificates.Inputs051.inputs_valid1037,?_⟩
  decide +kernel
theorem sound1037 : certificate1037.Sound :=
  rat_witness_certificate_sound certificate1037 valid1037 MajorityCertificates.Inputs051.envelope_sound1037

def certificate1038 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs051.envelope1038,(47/20),(991/5000),(2500426975050413791941/125000000000000000),(1726048893/1000000000),32,(1533445351/1000000000),0,(1125071799812462133/1000000000000000000),(630052554900869/1000000000000000000)⟩
theorem valid1038 : certificate1038.Valid := by
  refine ⟨MajorityCertificates.Inputs051.inputs_valid1038,?_⟩
  decide +kernel
theorem sound1038 : certificate1038.Sound :=
  rat_witness_certificate_sound certificate1038 valid1038 MajorityCertificates.Inputs051.envelope_sound1038

def certificate1039 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs051.envelope1039,(47/20),(63/200),(2500426975050413791941/125000000000000000),(1968659927/1000000000),32,(1007/1000),(368088186585304449/1000000000000000000),1,(4472588439023809/1000000000000000000)⟩
theorem valid1039 : certificate1039.Valid := by
  refine ⟨MajorityCertificates.Inputs051.inputs_valid1039,?_⟩
  decide +kernel
theorem sound1039 : certificate1039.Sound :=
  rat_witness_certificate_sound certificate1039 valid1039 MajorityCertificates.Inputs051.envelope_sound1039

def certificates : List RatWitnessCertificate := [certificate1020,certificate1021,certificate1022,certificate1023,certificate1024,certificate1025,certificate1026,certificate1027,certificate1028,certificate1029,certificate1030,certificate1031,certificate1032,certificate1033,certificate1034,certificate1035,certificate1036,certificate1037,certificate1038,certificate1039]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1020,List.forall_mem_cons.mpr ⟨sound1021,List.forall_mem_cons.mpr ⟨sound1022,List.forall_mem_cons.mpr ⟨sound1023,List.forall_mem_cons.mpr ⟨sound1024,List.forall_mem_cons.mpr ⟨sound1025,List.forall_mem_cons.mpr ⟨sound1026,List.forall_mem_cons.mpr ⟨sound1027,List.forall_mem_cons.mpr ⟨sound1028,List.forall_mem_cons.mpr ⟨sound1029,List.forall_mem_cons.mpr ⟨sound1030,List.forall_mem_cons.mpr ⟨sound1031,List.forall_mem_cons.mpr ⟨sound1032,List.forall_mem_cons.mpr ⟨sound1033,List.forall_mem_cons.mpr ⟨sound1034,List.forall_mem_cons.mpr ⟨sound1035,List.forall_mem_cons.mpr ⟨sound1036,List.forall_mem_cons.mpr ⟨sound1037,List.forall_mem_cons.mpr ⟨sound1038,List.forall_mem_cons.mpr ⟨sound1039,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch051
