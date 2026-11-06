import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs047

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch047

def certificate940 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs047.envelope940,(47/20),(61/200),(19336270263458644086213/500000000000000000),(36584973/20000000),32,(1007/1000),(92239667699041479/250000000000000000),1,(4472588439023811/1000000000000000000)⟩
theorem valid940 : certificate940.Valid := by
  refine ⟨MajorityCertificates.Inputs047.inputs_valid940,?_⟩
  decide +kernel
theorem sound940 : certificate940.Sound :=
  rat_witness_certificate_sound certificate940 valid940 MajorityCertificates.Inputs047.envelope_sound940

def certificate941 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs047.envelope941,(47/20),(453/2500),(9588827198051339616499/250000000000000000),(58674849/31250000),32,(119770729/250000000),0,1,(24566689586889/200000000000000000)⟩
theorem valid941 : certificate941.Valid := by
  refine ⟨MajorityCertificates.Inputs047.inputs_valid941,?_⟩
  decide +kernel
theorem sound941 : certificate941.Sound :=
  rat_witness_certificate_sound certificate941 valid941 MajorityCertificates.Inputs047.envelope_sound941

def certificate942 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs047.envelope942,(47/20),(453/2500),(9588827198051339616499/250000000000000000),(876635803/500000000),32,(378919383/250000000),0,(225007488962738983/200000000000000000),(258160154021677/1000000000000000000)⟩
theorem valid942 : certificate942.Valid := by
  refine ⟨MajorityCertificates.Inputs047.inputs_valid942,?_⟩
  decide +kernel
theorem sound942 : certificate942.Sound :=
  rat_witness_certificate_sound certificate942 valid942 MajorityCertificates.Inputs047.envelope_sound942

def certificate943 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs047.envelope943,(47/20),(61/200),(9588827198051339616499/250000000000000000),(916816751/500000000),32,(1007/1000),(368527027538085649/1000000000000000000),1,(1118147109755953/250000000000000000)⟩
theorem valid943 : certificate943.Valid := by
  refine ⟨MajorityCertificates.Inputs047.inputs_valid943,?_⟩
  decide +kernel
theorem sound943 : certificate943.Sound :=
  rat_witness_certificate_sound certificate943 valid943 MajorityCertificates.Inputs047.envelope_sound943

def certificate944 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs047.envelope944,(47/20),(7257/40000),(37951572089304756498021/1000000000000000000),(1878431199/1000000000),32,(479646141/1000000000),0,1,(124274241800469/1000000000000000000)⟩
theorem valid944 : certificate944.Valid := by
  refine ⟨MajorityCertificates.Inputs047.inputs_valid944,?_⟩
  decide +kernel
theorem sound944 : certificate944.Sound :=
  rat_witness_certificate_sound certificate944 valid944 MajorityCertificates.Inputs047.envelope_sound944

def certificate945 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs047.envelope945,(47/20),(7257/40000),(37951572089304756498021/1000000000000000000),(1753650493/1000000000),32,(757496123/500000000),0,(225007568633963751/200000000000000000),(265854406616503/1000000000000000000)⟩
theorem valid945 : certificate945.Valid := by
  refine ⟨MajorityCertificates.Inputs047.inputs_valid945,?_⟩
  decide +kernel
theorem sound945 : certificate945.Sound :=
  rat_witness_certificate_sound certificate945 valid945 MajorityCertificates.Inputs047.envelope_sound945

def certificate946 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs047.envelope946,(47/20),(61/200),(37951572089304756498021/1000000000000000000),(367054107/200000000),32,(503500019/500000000),(368367056378753077/1000000000000000000),1,(559078239069589/125000000000000000)⟩
theorem valid946 : certificate946.Valid := by
  refine ⟨MajorityCertificates.Inputs047.inputs_valid946,?_⟩
  decide +kernel
theorem sound946 : certificate946.Sound :=
  rat_witness_certificate_sound certificate946 valid946 MajorityCertificates.Inputs047.envelope_sound946

def certificate947 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs047.envelope947,(47/20),(3633/20000),(37555462999086581195769/1000000000000000000),(375853349/200000000),32,(48020971/100000000),0,1,(62753153971949/500000000000000000)⟩
theorem valid947 : certificate947.Valid := by
  refine ⟨MajorityCertificates.Inputs047.inputs_valid947,?_⟩
  decide +kernel
theorem sound947 : certificate947.Sound :=
  rat_witness_certificate_sound certificate947 valid947 MajorityCertificates.Inputs047.envelope_sound947

def certificate948 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs047.envelope948,(47/20),(3633/20000),(37555462999086581195769/1000000000000000000),(1753375293/1000000000),32,(378772393/250000000),0,(562519121161997401/500000000000000000),(16834617848867/62500000000000000)⟩
theorem valid948 : certificate948.Valid := by
  refine ⟨MajorityCertificates.Inputs047.inputs_valid948,?_⟩
  decide +kernel
theorem sound948 : certificate948.Sound :=
  rat_witness_certificate_sound certificate948 valid948 MajorityCertificates.Inputs047.envelope_sound948

def certificate949 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs047.envelope949,(47/20),(61/200),(37555462999086581195769/1000000000000000000),(1837463187/1000000000),32,(1007/1000),(46019207089686619/125000000000000000),1,(4472588439023811/1000000000000000000)⟩
theorem valid949 : certificate949.Valid := by
  refine ⟨MajorityCertificates.Inputs047.inputs_valid949,?_⟩
  decide +kernel
theorem sound949 : certificate949.Sound :=
  rat_witness_certificate_sound certificate949 valid949 MajorityCertificates.Inputs047.envelope_sound949

def certificate950 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs047.envelope950,(47/20),(291/1600),(18703095331422374979123/500000000000000000),(1880332057/1000000000),32,(480748999/1000000000),0,1,(31486744047483/250000000000000000)⟩
theorem valid950 : certificate950.Valid := by
  refine ⟨MajorityCertificates.Inputs047.inputs_valid950,?_⟩
  decide +kernel
theorem sound950 : certificate950.Sound :=
  rat_witness_certificate_sound certificate950 valid950 MajorityCertificates.Inputs047.envelope_sound950

def certificate951 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs047.envelope951,(47/20),(291/1600),(18703095331422374979123/500000000000000000),(1753346993/1000000000),32,(378712413/250000000),0,(1125038394937037587/1000000000000000000),(271051430171067/1000000000000000000)⟩
theorem valid951 : certificate951.Valid := by
  refine ⟨MajorityCertificates.Inputs047.inputs_valid951,?_⟩
  decide +kernel
theorem sound951 : certificate951.Sound :=
  rat_witness_certificate_sound certificate951 valid951 MajorityCertificates.Inputs047.envelope_sound951

def certificate952 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs047.envelope952,(47/20),(61/200),(18703095331422374979123/500000000000000000),(1839666717/1000000000),32,(1007/1000),(367940223063814347/1000000000000000000),1,(4472588439023811/1000000000000000000)⟩
theorem valid952 : certificate952.Valid := by
  refine ⟨MajorityCertificates.Inputs047.inputs_valid952,?_⟩
  decide +kernel
theorem sound952 : certificate952.Sound :=
  rat_witness_certificate_sound certificate952 valid952 MajorityCertificates.Inputs047.envelope_sound952

def certificate953 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs047.envelope953,(47/20),(14559/80000),(4651573464116167766979/125000000000000000),(1880712243/1000000000),32,(3848281/8000000),0,1,(126648454139871/1000000000000000000)⟩
theorem valid953 : certificate953.Valid := by
  refine ⟨MajorityCertificates.Inputs047.inputs_valid953,?_⟩
  decide +kernel
theorem sound953 : certificate953.Sound :=
  rat_witness_certificate_sound certificate953 valid953 MajorityCertificates.Inputs047.envelope_sound953

def certificate954 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs047.envelope954,(47/20),(14559/80000),(4651573464116167766979/125000000000000000),(876643227/500000000),32,(1514805897/1000000000),0,(225007718939326323/200000000000000000),(136386732449907/500000000000000000)⟩
theorem valid954 : certificate954.Valid := by
  refine ⟨MajorityCertificates.Inputs047.inputs_valid954,?_⟩
  decide +kernel
theorem sound954 : certificate954.Sound :=
  rat_witness_certificate_sound certificate954 valid954 MajorityCertificates.Inputs047.envelope_sound954

def certificate955 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs047.envelope955,(47/20),(61/200),(4651573464116167766979/125000000000000000),(920226727/500000000),32,(201400011/200000000),(367864331609475417/1000000000000000000),1,(4472642677031043/1000000000000000000)⟩
theorem valid955 : certificate955.Valid := by
  refine ⟨MajorityCertificates.Inputs047.inputs_valid955,?_⟩
  decide +kernel
theorem sound955 : certificate955.Sound :=
  rat_witness_certificate_sound certificate955 valid955 MajorityCertificates.Inputs047.envelope_sound955

def certificate956 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs047.envelope956,(47/20),(1811/10000),(36321210023289684453751/1000000000000000000),(1882125917/1000000000),32,(478316527/1000000000),0,1,(127322738155019/1000000000000000000)⟩
theorem valid956 : certificate956.Valid := by
  refine ⟨MajorityCertificates.Inputs047.inputs_valid956,?_⟩
  decide +kernel
theorem sound956 : certificate956.Sound :=
  rat_witness_certificate_sound certificate956 valid956 MajorityCertificates.Inputs047.envelope_sound956

def certificate957 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs047.envelope957,(47/20),(1811/10000),(36321210023289684453751/1000000000000000000),(43841131/25000000),32,(1515713857/1000000000),0,(1125039541895030851/1000000000000000000),(70054505648147/250000000000000000)⟩
theorem valid957 : certificate957.Valid := by
  refine ⟨MajorityCertificates.Inputs047.inputs_valid957,?_⟩
  decide +kernel
theorem sound957 : certificate957.Sound :=
  rat_witness_certificate_sound certificate957 valid957 MajorityCertificates.Inputs047.envelope_sound957

def certificate958 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs047.envelope958,(47/20),(31/100),(36321210023289684453751/1000000000000000000),(45684071/25000000),32,(1007/1000),(374668403489802983/1000000000000000000),1,(447258843902381/100000000000000000)⟩
theorem valid958 : certificate958.Valid := by
  refine ⟨MajorityCertificates.Inputs047.inputs_valid958,?_⟩
  decide +kernel
theorem sound958 : certificate958.Sound :=
  rat_witness_certificate_sound certificate958 valid958 MajorityCertificates.Inputs047.envelope_sound958

def certificate959 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs047.envelope959,(47/20),(3631/20000),(35594456451166953387459/1000000000000000000),(5891313/3125000),32,(95859309/200000000),0,1,(132504547579301/1000000000000000000)⟩
theorem valid959 : certificate959.Valid := by
  refine ⟨MajorityCertificates.Inputs047.inputs_valid959,?_⟩
  decide +kernel
theorem sound959 : certificate959.Sound :=
  rat_witness_certificate_sound certificate959 valid959 MajorityCertificates.Inputs047.envelope_sound959

def certificates : List RatWitnessCertificate := [certificate940,certificate941,certificate942,certificate943,certificate944,certificate945,certificate946,certificate947,certificate948,certificate949,certificate950,certificate951,certificate952,certificate953,certificate954,certificate955,certificate956,certificate957,certificate958,certificate959]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound940,List.forall_mem_cons.mpr ⟨sound941,List.forall_mem_cons.mpr ⟨sound942,List.forall_mem_cons.mpr ⟨sound943,List.forall_mem_cons.mpr ⟨sound944,List.forall_mem_cons.mpr ⟨sound945,List.forall_mem_cons.mpr ⟨sound946,List.forall_mem_cons.mpr ⟨sound947,List.forall_mem_cons.mpr ⟨sound948,List.forall_mem_cons.mpr ⟨sound949,List.forall_mem_cons.mpr ⟨sound950,List.forall_mem_cons.mpr ⟨sound951,List.forall_mem_cons.mpr ⟨sound952,List.forall_mem_cons.mpr ⟨sound953,List.forall_mem_cons.mpr ⟨sound954,List.forall_mem_cons.mpr ⟨sound955,List.forall_mem_cons.mpr ⟨sound956,List.forall_mem_cons.mpr ⟨sound957,List.forall_mem_cons.mpr ⟨sound958,List.forall_mem_cons.mpr ⟨sound959,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch047
