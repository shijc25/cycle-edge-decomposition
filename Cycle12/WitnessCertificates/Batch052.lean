import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs052

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch052

def certificate1040 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs052.envelope1040,(47/20),(1991/10000),(19575556805189512953233/1000000000000000000),(1955947481/1000000000),32,(130986179/250000000),0,1,(31212214861383/125000000000000000)⟩
theorem valid1040 : certificate1040.Valid := by
  refine ⟨MajorityCertificates.Inputs052.inputs_valid1040,?_⟩
  decide +kernel
theorem sound1040 : certificate1040.Sound :=
  rat_witness_certificate_sound certificate1040 valid1040 MajorityCertificates.Inputs052.envelope_sound1040

def certificate1041 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs052.envelope1041,(47/20),(1991/10000),(19575556805189512953233/1000000000000000000),(862163873/500000000),32,(383701719/250000000),0,(1125073369206077483/1000000000000000000),(20361797746337/31250000000000000)⟩
theorem valid1041 : certificate1041.Valid := by
  refine ⟨MajorityCertificates.Inputs052.inputs_valid1041,?_⟩
  decide +kernel
theorem sound1041 : certificate1041.Sound :=
  rat_witness_certificate_sound certificate1041 valid1041 MajorityCertificates.Inputs052.envelope_sound1041

def certificate1042 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs052.envelope1042,(47/20),(63/200),(19575556805189512953233/1000000000000000000),(494325307/250000000),32,(125875001/125000000),(73493171243800067/200000000000000000),1,(1118149082047217/250000000000000000)⟩
theorem valid1042 : certificate1042.Valid := by
  refine ⟨MajorityCertificates.Inputs052.inputs_valid1042,?_⟩
  decide +kernel
theorem sound1042 : certificate1042.Sound :=
  rat_witness_certificate_sound certificate1042 valid1042 MajorityCertificates.Inputs052.envelope_sound1042

def certificate1043 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs052.envelope1043,(47/20),(197/1000),(19169980940630702698633/1000000000000000000),(492541139/250000000),32,(516425781/1000000000),0,1,(249615196275019/1000000000000000000)⟩
theorem valid1043 : certificate1043.Valid := by
  refine ⟨MajorityCertificates.Inputs052.inputs_valid1043,?_⟩
  decide +kernel
theorem sound1043 : certificate1043.Sound :=
  rat_witness_certificate_sound certificate1043 valid1043 MajorityCertificates.Inputs052.envelope_sound1043

def certificate1044 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs052.envelope1044,(47/20),(197/1000),(19169980940630702698633/1000000000000000000),(26956337/15625000),32,(768316109/500000000),0,(17579295649151177/15625000000000000),(727974437435781/1000000000000000000)⟩
theorem valid1044 : certificate1044.Valid := by
  refine ⟨MajorityCertificates.Inputs052.inputs_valid1044,?_⟩
  decide +kernel
theorem sound1044 : certificate1044.Sound :=
  rat_witness_certificate_sound certificate1044 valid1044 MajorityCertificates.Inputs052.envelope_sound1044

def certificate1045 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs052.envelope1045,(47/20),(63/200),(19169980940630702698633/1000000000000000000),(992747497/500000000),32,(251750557/250000000),(73377531214952619/200000000000000000),1,(2237392783324173/500000000000000000)⟩
theorem valid1045 : certificate1045.Valid := by
  refine ⟨MajorityCertificates.Inputs052.inputs_valid1045,?_⟩
  decide +kernel
theorem sound1045 : certificate1045.Sound :=
  rat_witness_certificate_sound certificate1045 valid1045 MajorityCertificates.Inputs052.envelope_sound1045

def certificate1046 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs052.envelope1046,(47/20),(2079/10000),(18785377548995781000869/1000000000000000000),(1941478957/1000000000),32,(551765303/1000000000),0,1,(132709053526793/500000000000000000)⟩
theorem valid1046 : certificate1046.Valid := by
  refine ⟨MajorityCertificates.Inputs052.inputs_valid1046,?_⟩
  decide +kernel
theorem sound1046 : certificate1046.Sound :=
  rat_witness_certificate_sound certificate1046 valid1046 MajorityCertificates.Inputs052.envelope_sound1046

def certificate1047 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs052.envelope1047,(47/20),(2079/10000),(18785377548995781000869/1000000000000000000),(1716467739/1000000000),32,(153492687/100000000),0,(562538227768432959/500000000000000000),(645381508174461/1000000000000000000)⟩
theorem valid1047 : certificate1047.Valid := by
  refine ⟨MajorityCertificates.Inputs052.inputs_valid1047,?_⟩
  decide +kernel
theorem sound1047 : certificate1047.Sound :=
  rat_witness_certificate_sound certificate1047 valid1047 MajorityCertificates.Inputs052.envelope_sound1047

def certificate1048 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs052.envelope1048,(47/20),(63/200),(18785377548995781000869/1000000000000000000),(398945721/200000000),32,(1007/1000),(91561741874109819/250000000000000000),1,(4472588439023811/1000000000000000000)⟩
theorem valid1048 : certificate1048.Valid := by
  refine ⟨MajorityCertificates.Inputs052.inputs_valid1048,?_⟩
  decide +kernel
theorem sound1048 : certificate1048.Sound :=
  rat_witness_certificate_sound certificate1048 valid1048 MajorityCertificates.Inputs052.envelope_sound1048

def certificate1049 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs052.envelope1049,(47/20),(261/1250),(9210269669224913247457/500000000000000000),(972722037/500000000),32,(277058739/500000000),0,1,(271515995396759/1000000000000000000)⟩
theorem valid1049 : certificate1049.Valid := by
  refine ⟨MajorityCertificates.Inputs052.inputs_valid1049,?_⟩
  decide +kernel
theorem sound1049 : certificate1049.Sound :=
  rat_witness_certificate_sound certificate1049 valid1049 MajorityCertificates.Inputs052.envelope_sound1049

def certificate1050 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs052.envelope1050,(47/20),(261/1250),(9210269669224913247457/500000000000000000),(428153531/250000000),32,(1539175511/1000000000),0,(112507796990104141/100000000000000000),(179404889715899/250000000000000000)⟩
theorem valid1050 : certificate1050.Valid := by
  refine ⟨MajorityCertificates.Inputs052.inputs_valid1050,?_⟩
  decide +kernel
theorem sound1050 : certificate1050.Sound :=
  rat_witness_certificate_sound certificate1050 valid1050 MajorityCertificates.Inputs052.envelope_sound1050

def certificate1051 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs052.envelope1051,(47/20),(63/200),(9210269669224913247457/500000000000000000),(2003515287/1000000000),32,(1007/1000),(182825145315082089/500000000000000000),1,(447258843902381/100000000000000000)⟩
theorem valid1051 : certificate1051.Valid := by
  refine ⟨MajorityCertificates.Inputs052.inputs_valid1051,?_⟩
  decide +kernel
theorem sound1051 : certificate1051.Sound :=
  rat_witness_certificate_sound certificate1051 valid1051 MajorityCertificates.Inputs052.envelope_sound1051

def certificate1052 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs052.envelope1052,(47/20),(2097/10000),(18074352963374871742289/1000000000000000000),(389896191/200000000),32,(69558693/125000000),0,1,(277080124548891/1000000000000000000)⟩
theorem valid1052 : certificate1052.Valid := by
  refine ⟨MajorityCertificates.Inputs052.inputs_valid1052,?_⟩
  decide +kernel
theorem sound1052 : certificate1052.Sound :=
  rat_witness_certificate_sound certificate1052 valid1052 MajorityCertificates.Inputs052.envelope_sound1052

def certificate1053 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs052.envelope1053,(47/20),(2097/10000),(18074352963374871742289/1000000000000000000),(1676192957/1000000000),32,(793515997/500000000),0,(562539731688186261/500000000000000000),(399166208000637/1000000000000000000)⟩
theorem valid1053 : certificate1053.Valid := by
  refine ⟨MajorityCertificates.Inputs052.inputs_valid1053,?_⟩
  decide +kernel
theorem sound1053 : certificate1053.Sound :=
  rat_witness_certificate_sound certificate1053 valid1053 MajorityCertificates.Inputs052.envelope_sound1053

def certificate1054 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs052.envelope1054,(47/20),(63/200),(18074352963374871742289/1000000000000000000),(50308623/25000000),32,(1007/1000),(365062444467354259/1000000000000000000),1,(4472588439023811/1000000000000000000)⟩
theorem valid1054 : certificate1054.Valid := by
  refine ⟨MajorityCertificates.Inputs052.inputs_valid1054,?_⟩
  decide +kernel
theorem sound1054 : certificate1054.Sound :=
  rat_witness_certificate_sound certificate1054 valid1054 MajorityCertificates.Inputs052.envelope_sound1054

def certificate1055 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs052.envelope1055,(47/20),(1053/5000),(4436447651108718332133/250000000000000000),(1955164349/1000000000),32,(558665087/1000000000),0,1,(263687729781261/1000000000000000000)⟩
theorem valid1055 : certificate1055.Valid := by
  refine ⟨MajorityCertificates.Inputs052.inputs_valid1055,?_⟩
  decide +kernel
theorem sound1055 : certificate1055.Sound :=
  rat_witness_certificate_sound certificate1055 valid1055 MajorityCertificates.Inputs052.envelope_sound1055

def certificate1056 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs052.envelope1056,(47/20),(1053/5000),(4436447651108718332133/250000000000000000),(1707605567/1000000000),32,(308822449/200000000),0,(1125080934718837137/1000000000000000000),(151247576645089/200000000000000000)⟩
theorem valid1056 : certificate1056.Valid := by
  refine ⟨MajorityCertificates.Inputs052.inputs_valid1056,?_⟩
  decide +kernel
theorem sound1056 : certificate1056.Sound :=
  rat_witness_certificate_sound certificate1056 valid1056 MajorityCertificates.Inputs052.envelope_sound1056

def certificate1057 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs052.envelope1057,(47/20),(63/200),(4436447651108718332133/250000000000000000),(2021215183/1000000000),32,(503500029/500000000),(182241766465305609/500000000000000000),1,(4472645635467631/1000000000000000000)⟩
theorem valid1057 : certificate1057.Valid := by
  refine ⟨MajorityCertificates.Inputs052.inputs_valid1057,?_⟩
  decide +kernel
theorem sound1057 : certificate1057.Sound :=
  rat_witness_certificate_sound certificate1057 valid1057 MajorityCertificates.Inputs052.envelope_sound1057

def certificate1058 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs052.envelope1058,(47/20),(423/2000),(272404725454788921341/15625000000000000),(1954724627/1000000000),32,(17545361/31250000),0,1,(264544627853239/1000000000000000000)⟩
theorem valid1058 : certificate1058.Valid := by
  refine ⟨MajorityCertificates.Inputs052.inputs_valid1058,?_⟩
  decide +kernel
theorem sound1058 : certificate1058.Sound :=
  rat_witness_certificate_sound certificate1058 valid1058 MajorityCertificates.Inputs052.envelope_sound1058

def certificate1059 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs052.envelope1059,(47/20),(423/2000),(272404725454788921341/15625000000000000),(170611637/100000000),32,(309062339/200000000),0,(562541191351639567/500000000000000000),(394190300226827/500000000000000000)⟩
theorem valid1059 : certificate1059.Valid := by
  refine ⟨MajorityCertificates.Inputs052.inputs_valid1059,?_⟩
  decide +kernel
theorem sound1059 : certificate1059.Sound :=
  rat_witness_certificate_sound certificate1059 valid1059 MajorityCertificates.Inputs052.envelope_sound1059

def certificates : List RatWitnessCertificate := [certificate1040,certificate1041,certificate1042,certificate1043,certificate1044,certificate1045,certificate1046,certificate1047,certificate1048,certificate1049,certificate1050,certificate1051,certificate1052,certificate1053,certificate1054,certificate1055,certificate1056,certificate1057,certificate1058,certificate1059]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound1040,List.forall_mem_cons.mpr ⟨sound1041,List.forall_mem_cons.mpr ⟨sound1042,List.forall_mem_cons.mpr ⟨sound1043,List.forall_mem_cons.mpr ⟨sound1044,List.forall_mem_cons.mpr ⟨sound1045,List.forall_mem_cons.mpr ⟨sound1046,List.forall_mem_cons.mpr ⟨sound1047,List.forall_mem_cons.mpr ⟨sound1048,List.forall_mem_cons.mpr ⟨sound1049,List.forall_mem_cons.mpr ⟨sound1050,List.forall_mem_cons.mpr ⟨sound1051,List.forall_mem_cons.mpr ⟨sound1052,List.forall_mem_cons.mpr ⟨sound1053,List.forall_mem_cons.mpr ⟨sound1054,List.forall_mem_cons.mpr ⟨sound1055,List.forall_mem_cons.mpr ⟨sound1056,List.forall_mem_cons.mpr ⟨sound1057,List.forall_mem_cons.mpr ⟨sound1058,List.forall_mem_cons.mpr ⟨sound1059,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch052
