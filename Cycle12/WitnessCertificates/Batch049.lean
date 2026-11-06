import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs049

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch049

def certificate980 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs049.envelope980,(47/20),(477/2500),(31583197446211058204217/1000000000000000000),(1871419023/1000000000),32,(253907787/500000000),0,1,(7617433699891/50000000000000000)⟩
theorem valid980 : certificate980.Valid := by
  refine ⟨MajorityCertificates.Inputs049.inputs_valid980,?_⟩
  decide +kernel
theorem sound980 : certificate980.Sound :=
  rat_witness_certificate_sound certificate980 valid980 MajorityCertificates.Inputs049.envelope_sound980

def certificate981 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs049.envelope981,(47/20),(477/2500),(31583197446211058204217/1000000000000000000),(1743260723/1000000000),32,(758364851/500000000),0,(1125045474033039823/1000000000000000000),(66485859987471/200000000000000000)⟩
theorem valid981 : certificate981.Valid := by
  refine ⟨MajorityCertificates.Inputs049.inputs_valid981,?_⟩
  decide +kernel
theorem sound981 : certificate981.Sound :=
  rat_witness_certificate_sound certificate981 valid981 MajorityCertificates.Inputs049.envelope_sound981

def certificate982 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs049.envelope982,(47/20),(31/100),(31583197446211058204217/1000000000000000000),(924849257/500000000),32,(1007/1000),(11640537500519597/31250000000000000),1,(447258843902381/100000000000000000)⟩
theorem valid982 : certificate982.Valid := by
  refine ⟨MajorityCertificates.Inputs049.inputs_valid982,?_⟩
  decide +kernel
theorem sound982 : certificate982.Sound :=
  rat_witness_certificate_sound certificate982 valid982 MajorityCertificates.Inputs049.envelope_sound982

def certificate983 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs049.envelope983,(47/20),(1917/10000),(3809134603006935974091/125000000000000000),(1874792887/1000000000),32,(63762993/125000000),0,1,(158125233900229/1000000000000000000)⟩
theorem valid983 : certificate983.Valid := by
  refine ⟨MajorityCertificates.Inputs049.inputs_valid983,?_⟩
  decide +kernel
theorem sound983 : certificate983.Sound :=
  rat_witness_certificate_sound certificate983 valid983 MajorityCertificates.Inputs049.envelope_sound983

def certificate984 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs049.envelope984,(47/20),(1917/10000),(3809134603006935974091/125000000000000000),(174220977/100000000),32,(758583229/500000000),0,(225009426137159431/200000000000000000),(348284148665021/1000000000000000000)⟩
theorem valid984 : certificate984.Valid := by
  refine ⟨MajorityCertificates.Inputs049.inputs_valid984,?_⟩
  decide +kernel
theorem sound984 : certificate984.Sound :=
  rat_witness_certificate_sound certificate984 valid984 MajorityCertificates.Inputs049.envelope_sound984

def certificate985 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs049.envelope985,(47/20),(31/100),(3809134603006935974091/125000000000000000),(931540491/500000000),32,(201402399/200000000),(371252053680572447/1000000000000000000),1,(280276069692237/62500000000000000)⟩
theorem valid985 : certificate985.Valid := by
  refine ⟨MajorityCertificates.Inputs049.inputs_valid985,?_⟩
  decide +kernel
theorem sound985 : certificate985.Sound :=
  rat_witness_certificate_sound certificate985 valid985 MajorityCertificates.Inputs049.envelope_sound985

def certificate986 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs049.envelope986,(47/20),(116/625),(30100436419524438813219/1000000000000000000),(190081317/100000000),32,(30591451/62500000),0,1,(157949977131233/1000000000000000000)⟩
theorem valid986 : certificate986.Valid := by
  refine ⟨MajorityCertificates.Inputs049.inputs_valid986,?_⟩
  decide +kernel
theorem sound986 : certificate986.Sound :=
  rat_witness_certificate_sound certificate986 valid986 MajorityCertificates.Inputs049.envelope_sound986

def certificate987 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs049.envelope987,(47/20),(116/625),(30100436419524438813219/1000000000000000000),(3431266/1953125),32,(301484161/200000000),0,(562523857089119921/500000000000000000),(177534789677309/500000000000000000)⟩
theorem valid987 : certificate987.Valid := by
  refine ⟨MajorityCertificates.Inputs049.inputs_valid987,?_⟩
  decide +kernel
theorem sound987 : certificate987.Sound :=
  rat_witness_certificate_sound certificate987 valid987 MajorityCertificates.Inputs049.envelope_sound987

def certificate988 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs049.envelope988,(47/20),(63/200),(30100436419524438813219/1000000000000000000),(1853187087/1000000000),32,(1007/1000),(47210094125576409/125000000000000000),1,(1118147109755953/250000000000000000)⟩
theorem valid988 : certificate988.Valid := by
  refine ⟨MajorityCertificates.Inputs049.inputs_valid988,?_⟩
  decide +kernel
theorem sound988 : certificate988.Sound :=
  rat_witness_certificate_sound certificate988 valid988 MajorityCertificates.Inputs049.envelope_sound988

def certificate989 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs049.envelope989,(47/20),(3721/20000),(14794134009094345190263/500000000000000000),(1902560831/1000000000),32,(490598817/1000000000),0,1,(160771916484191/1000000000000000000)⟩
theorem valid989 : certificate989.Valid := by
  refine ⟨MajorityCertificates.Inputs049.inputs_valid989,?_⟩
  decide +kernel
theorem sound989 : certificate989.Sound :=
  rat_witness_certificate_sound certificate989 valid989 MajorityCertificates.Inputs049.envelope_sound989

def certificate990 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs049.envelope990,(47/20),(3721/20000),(14794134009094345190263/500000000000000000),(1747867457/1000000000),32,(1517686243/1000000000),0,(1125048540131096079/1000000000000000000),(182249298272803/500000000000000000)⟩
theorem valid990 : certificate990.Valid := by
  refine ⟨MajorityCertificates.Inputs049.inputs_valid990,?_⟩
  decide +kernel
theorem sound990 : certificate990.Sound :=
  rat_witness_certificate_sound certificate990 valid990 MajorityCertificates.Inputs049.envelope_sound990

def certificate991 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs049.envelope991,(47/20),(63/200),(14794134009094345190263/500000000000000000),(232160891/125000000),32,(1007/1000),(377295515930340419/1000000000000000000),1,(4472588439023811/1000000000000000000)⟩
theorem valid991 : certificate991.Valid := by
  refine ⟨MajorityCertificates.Inputs049.inputs_valid991,?_⟩
  decide +kernel
theorem sound991 : certificate991.Sound :=
  rat_witness_certificate_sound certificate991 valid991 MajorityCertificates.Inputs049.envelope_sound991

def certificate992 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs049.envelope992,(47/20),(373/2000),(14546364203705432194003/500000000000000000),(1904315297/1000000000),32,(98347051/200000000),0,1,(81813792930503/500000000000000000)⟩
theorem valid992 : certificate992.Valid := by
  refine ⟨MajorityCertificates.Inputs049.inputs_valid992,?_⟩
  decide +kernel
theorem sound992 : certificate992.Sound :=
  rat_witness_certificate_sound certificate992 valid992 MajorityCertificates.Inputs049.envelope_sound992

def certificate993 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs049.envelope993,(47/20),(373/2000),(14546364203705432194003/500000000000000000),(349436733/200000000),32,(60722959/40000000),0,(562524683474326389/500000000000000000),(372710636007331/1000000000000000000)⟩
theorem valid993 : certificate993.Valid := by
  refine ⟨MajorityCertificates.Inputs049.inputs_valid993,?_⟩
  decide +kernel
theorem sound993 : certificate993.Sound :=
  rat_witness_certificate_sound certificate993 valid993 MajorityCertificates.Inputs049.envelope_sound993

def certificate994 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs049.envelope994,(47/20),(63/200),(14546364203705432194003/500000000000000000),(1861388863/1000000000),32,(1007/1000),(75382737139637043/200000000000000000),1,(447258843902381/100000000000000000)⟩
theorem valid994 : certificate994.Valid := by
  refine ⟨MajorityCertificates.Inputs049.inputs_valid994,?_⟩
  decide +kernel
theorem sound994 : certificate994.Sound :=
  rat_witness_certificate_sound certificate994 valid994 MajorityCertificates.Inputs049.envelope_sound994

def certificate995 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs049.envelope995,(47/20),(3739/20000),(894160117241170598371/31250000000000000),(1906077249/1000000000),32,(492872459/1000000000),0,1,(166490763811329/1000000000000000000)⟩
theorem valid995 : certificate995.Valid := by
  refine ⟨MajorityCertificates.Inputs049.inputs_valid995,?_⟩
  decide +kernel
theorem sound995 : certificate995.Sound :=
  rat_witness_certificate_sound certificate995 valid995 MajorityCertificates.Inputs049.envelope_sound995

def certificate996 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs049.envelope996,(47/20),(3739/20000),(894160117241170598371/31250000000000000),(873580633/500000000),32,(758830343/500000000),0,(1125050194451453453/1000000000000000000),(47541965172743/125000000000000000)⟩
theorem valid996 : certificate996.Valid := by
  refine ⟨MajorityCertificates.Inputs049.inputs_valid996,?_⟩
  decide +kernel
theorem sound996 : certificate996.Sound :=
  rat_witness_certificate_sound certificate996 valid996 MajorityCertificates.Inputs049.envelope_sound996

def certificate997 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs049.envelope997,(47/20),(63/200),(894160117241170598371/31250000000000000),(93274701/50000000),32,(1007/1000),(376535074090418581/1000000000000000000),1,(447258843902381/100000000000000000)⟩
theorem valid997 : certificate997.Valid := by
  refine ⟨MajorityCertificates.Inputs049.inputs_valid997,?_⟩
  decide +kernel
theorem sound997 : certificate997.Sound :=
  rat_witness_certificate_sound certificate997 valid997 MajorityCertificates.Inputs049.envelope_sound997

def certificate998 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs049.envelope998,(47/20),(937/5000),(3518599610248635872887/125000000000000000),(1907847203/1000000000),32,(123502597/250000000),0,1,(42342499172541/250000000000000000)⟩
theorem valid998 : certificate998.Valid := by
  refine ⟨MajorityCertificates.Inputs049.inputs_valid998,?_⟩
  decide +kernel
theorem sound998 : certificate998.Sound :=
  rat_witness_certificate_sound certificate998 valid998 MajorityCertificates.Inputs049.envelope_sound998

def certificate999 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs049.envelope999,(47/20),(937/5000),(3518599610248635872887/125000000000000000),(1746058129/1000000000),32,(189820451/125000000),0,(562525511230182239/500000000000000000),(389437530223959/1000000000000000000)⟩
theorem valid999 : certificate999.Valid := by
  refine ⟨MajorityCertificates.Inputs049.inputs_valid999,?_⟩
  decide +kernel
theorem sound999 : certificate999.Sound :=
  rat_witness_certificate_sound certificate999 valid999 MajorityCertificates.Inputs049.envelope_sound999

def certificates : List RatWitnessCertificate := [certificate980,certificate981,certificate982,certificate983,certificate984,certificate985,certificate986,certificate987,certificate988,certificate989,certificate990,certificate991,certificate992,certificate993,certificate994,certificate995,certificate996,certificate997,certificate998,certificate999]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound980,List.forall_mem_cons.mpr ⟨sound981,List.forall_mem_cons.mpr ⟨sound982,List.forall_mem_cons.mpr ⟨sound983,List.forall_mem_cons.mpr ⟨sound984,List.forall_mem_cons.mpr ⟨sound985,List.forall_mem_cons.mpr ⟨sound986,List.forall_mem_cons.mpr ⟨sound987,List.forall_mem_cons.mpr ⟨sound988,List.forall_mem_cons.mpr ⟨sound989,List.forall_mem_cons.mpr ⟨sound990,List.forall_mem_cons.mpr ⟨sound991,List.forall_mem_cons.mpr ⟨sound992,List.forall_mem_cons.mpr ⟨sound993,List.forall_mem_cons.mpr ⟨sound994,List.forall_mem_cons.mpr ⟨sound995,List.forall_mem_cons.mpr ⟨sound996,List.forall_mem_cons.mpr ⟨sound997,List.forall_mem_cons.mpr ⟨sound998,List.forall_mem_cons.mpr ⟨sound999,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch049
