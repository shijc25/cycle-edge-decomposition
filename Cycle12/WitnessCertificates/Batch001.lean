import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs001

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch001

def certificate20 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs001.envelope20,(225527/100000),(143676563/1000000000),(307769565671236112583/100000000000000000),(1862068319/1000000000),(3/2),(15394619/40000000),0,1,(150250332660399/100000000000000000)⟩
theorem valid20 : certificate20.Valid := by
  refine ⟨MajorityCertificates.Inputs001.inputs_valid20,?_⟩
  decide +kernel
theorem sound20 : certificate20.Sound :=
  rat_witness_certificate_sound certificate20 valid20 MajorityCertificates.Inputs001.envelope_sound20

def certificate21 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs001.envelope21,(225527/100000),(143676563/1000000000),(307769565671236112583/100000000000000000),(2217509053/1000000000),(3/2),(628562329/500000000),0,(70342900140804689/62500000000000000),(1233979456706409/1000000000000000000)⟩
theorem valid21 : certificate21.Valid := by
  refine ⟨MajorityCertificates.Inputs001.inputs_valid21,?_⟩
  decide +kernel
theorem sound21 : certificate21.Sound :=
  rat_witness_certificate_sound certificate21 valid21 MajorityCertificates.Inputs001.envelope_sound21

def certificate22 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs001.envelope22,(224413/100000),(72160547/500000000),(660788289044395744131/250000000000000000),(1869852597/1000000000),(31/20),(386953451/1000000000),0,1,(1754943304028229/1000000000000000000)⟩
theorem valid22 : certificate22.Valid := by
  refine ⟨MajorityCertificates.Inputs001.inputs_valid22,?_⟩
  decide +kernel
theorem sound22 : certificate22.Sound :=
  rat_witness_certificate_sound certificate22 valid22 MajorityCertificates.Inputs001.envelope_sound22

def certificate23 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs001.envelope23,(224413/100000),(72160547/500000000),(660788289044395744131/250000000000000000),(278851353/125000000),(31/20),(627945439/500000000),0,(1125569212338408663/1000000000000000000),(176737251157081/125000000000000000)⟩
theorem valid23 : certificate23.Valid := by
  refine ⟨MajorityCertificates.Inputs001.inputs_valid23,?_⟩
  decide +kernel
theorem sound23 : certificate23.Sound :=
  rat_witness_certificate_sound certificate23 valid23 MajorityCertificates.Inputs001.envelope_sound23

def certificate24 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs001.envelope24,(223329/100000),(46389/320000),(2297201253456370845709/1000000000000000000),(938486569/500000000),(31/20),(389110911/1000000000),0,1,(505516488775153/250000000000000000)⟩
theorem valid24 : certificate24.Valid := by
  refine ⟨MajorityCertificates.Inputs001.inputs_valid24,?_⟩
  decide +kernel
theorem sound24 : certificate24.Sound :=
  rat_witness_certificate_sound certificate24 valid24 MajorityCertificates.Inputs001.envelope_sound24

def certificate25 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs001.envelope25,(223329/100000),(46389/320000),(2297201253456370845709/1000000000000000000),(2239145353/1000000000),(31/20),(125684849/100000000),0,(562829076732099763/500000000000000000),(1635947489286017/1000000000000000000)⟩
theorem valid25 : certificate25.Valid := by
  refine ⟨MajorityCertificates.Inputs001.inputs_valid25,?_⟩
  decide +kernel
theorem sound25 : certificate25.Sound :=
  rat_witness_certificate_sound certificate25 valid25 MajorityCertificates.Inputs001.envelope_sound25

def certificate26 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs001.envelope26,(111137/50000),(36402539/250000000),(252147263830554027219/125000000000000000),(942257997/500000000),(31/20),(9780439/25000000),0,1,(2311319861256907/1000000000000000000)⟩
theorem valid26 : certificate26.Valid := by
  refine ⟨MajorityCertificates.Inputs001.inputs_valid26,?_⟩
  decide +kernel
theorem sound26 : certificate26.Sound :=
  rat_witness_certificate_sound certificate26 valid26 MajorityCertificates.Inputs001.envelope_sound26

def certificate27 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs001.envelope27,(111137/50000),(36402539/250000000),(252147263830554027219/125000000000000000),(224732931/100000000),(31/20),(1257857799/1000000000),0,(562876562379113021/500000000000000000),(936740503969243/500000000000000000)⟩
theorem valid27 : certificate27.Valid := by
  refine ⟨MajorityCertificates.Inputs001.inputs_valid27,?_⟩
  decide +kernel
theorem sound27 : certificate27.Sound :=
  rat_witness_certificate_sound certificate27 valid27 MajorityCertificates.Inputs001.envelope_sound27

def certificate28 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs001.envelope28,(110623/50000),(4570459/31250000),(893623095659599263587/500000000000000000),(29552683/15625000),(31/20),(196698639/500000000),0,1,(2613094495914267/1000000000000000000)⟩
theorem valid28 : certificate28.Valid := by
  refine ⟨MajorityCertificates.Inputs001.inputs_valid28,?_⟩
  decide +kernel
theorem sound28 : certificate28.Sound :=
  rat_witness_certificate_sound certificate28 valid28 MajorityCertificates.Inputs001.envelope_sound28

def certificate29 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs001.envelope29,(110623/50000),(4570459/31250000),(893623095659599263587/500000000000000000),(2255375033/1000000000),(31/20),(157364791/125000000),0,(562927012225284077/500000000000000000),(1063146094232823/500000000000000000)⟩
theorem valid29 : certificate29.Valid := by
  refine ⟨MajorityCertificates.Inputs001.inputs_valid29,?_⟩
  decide +kernel
theorem sound29 : certificate29.Sound :=
  rat_witness_certificate_sound certificate29 valid29 MajorityCertificates.Inputs001.envelope_sound29

def certificate30 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs001.envelope30,(44049/20000),(146899219/1000000000),(199508041444546027759/125000000000000000),(947348241/500000000),(31/20),(395968167/1000000000),0,1,(365095348420713/125000000000000000)⟩
theorem valid30 : certificate30.Valid := by
  refine ⟨MajorityCertificates.Inputs001.inputs_valid30,?_⟩
  decide +kernel
theorem sound30 : certificate30.Sound :=
  rat_witness_certificate_sound certificate30 valid30 MajorityCertificates.Inputs001.envelope_sound30

def certificate31 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs001.envelope31,(44049/20000),(146899219/1000000000),(199508041444546027759/125000000000000000),(282909897/125000000),(31/20),(1260028667/1000000000),0,(1125960739575060743/1000000000000000000),(2394194563464213/1000000000000000000)⟩
theorem valid31 : certificate31.Valid := by
  refine ⟨MajorityCertificates.Inputs001.inputs_valid31,?_⟩
  decide +kernel
theorem sound31 : certificate31.Sound :=
  rat_witness_certificate_sound certificate31 valid31 MajorityCertificates.Inputs001.envelope_sound31

def certificate32 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs001.envelope32,(21927/10000),(23607/160000),(179417096775373226307/125000000000000000),(1905070769/1000000000),(31/20),(198874883/500000000),0,1,(327519952716519/100000000000000000)⟩
theorem valid32 : certificate32.Valid := by
  refine ⟨MajorityCertificates.Inputs001.inputs_valid32,?_⟩
  decide +kernel
theorem sound32 : certificate32.Sound :=
  rat_witness_certificate_sound certificate32 valid32 MajorityCertificates.Inputs001.envelope_sound32

def certificate33 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs001.envelope33,(21927/10000),(23607/160000),(179417096775373226307/125000000000000000),(2271045873/1000000000),(31/20),(630594099/500000000),0,(563036577962845477/500000000000000000),(4283206528999/1600000000000000)⟩
theorem valid33 : certificate33.Valid := by
  refine ⟨MajorityCertificates.Inputs001.inputs_valid33,?_⟩
  decide +kernel
theorem sound33 : certificate33.Sound :=
  rat_witness_certificate_sound certificate33 valid33 MajorityCertificates.Inputs001.envelope_sound33

def certificate34 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs001.envelope34,(2729/1250),(148188281/1000000000),(649440413585474310029/500000000000000000),(1911461307/1000000000),(8/5),(399971993/1000000000),0,1,(1813591908765723/500000000000000000)⟩
theorem valid34 : certificate34.Valid := by
  refine ⟨MajorityCertificates.Inputs001.inputs_valid34,?_⟩
  decide +kernel
theorem sound34 : certificate34.Sound :=
  rat_witness_certificate_sound certificate34 valid34 MajorityCertificates.Inputs001.envelope_sound34

def certificate35 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs001.envelope35,(2729/1250),(148188281/1000000000),(649440413585474310029/500000000000000000),(1140185293/500000000),(8/5),(630925917/500000000),0,(225238231080624241/200000000000000000),(2966130210430157/1000000000000000000)⟩
theorem valid35 : certificate35.Valid := by
  refine ⟨MajorityCertificates.Inputs001.inputs_valid35,?_⟩
  decide +kernel
theorem sound35 : certificate35.Sound :=
  rat_witness_certificate_sound certificate35 valid35 MajorityCertificates.Inputs001.envelope_sound35

def certificate36 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs001.envelope36,(217393/100000),(148832813/1000000000),(1182011536263273450937/1000000000000000000),(1918241053/1000000000),(8/5),(100538301/250000000),0,1,(2003923153499129/500000000000000000)⟩
theorem valid36 : certificate36.Valid := by
  refine ⟨MajorityCertificates.Inputs001.inputs_valid36,?_⟩
  decide +kernel
theorem sound36 : certificate36.Sound :=
  rat_witness_certificate_sound certificate36 valid36 MajorityCertificates.Inputs001.envelope_sound36

def certificate37 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs001.envelope37,(217393/100000),(148832813/1000000000),(1182011536263273450937/1000000000000000000),(1143990749/500000000),(8/5),(4933939/3906250),0,(281578655591612643/250000000000000000),(3276802490365389/1000000000000000000)⟩
theorem valid37 : certificate37.Valid := by
  refine ⟨MajorityCertificates.Inputs001.inputs_valid37,?_⟩
  decide +kernel
theorem sound37 : certificate37.Sound :=
  rat_witness_certificate_sound certificate37 valid37 MajorityCertificates.Inputs001.envelope_sound37

def certificate38 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs001.envelope38,(8647/4000),(148832813/1000000000),(135140731992612482481/125000000000000000),(77088557/40000000),(8/5),(80519787/200000000),0,1,(4394258692189677/1000000000000000000)⟩
theorem valid38 : certificate38.Valid := by
  refine ⟨MajorityCertificates.Inputs001.inputs_valid38,?_⟩
  decide +kernel
theorem sound38 : certificate38.Sound :=
  rat_witness_certificate_sound certificate38 valid38 MajorityCertificates.Inputs001.envelope_sound38

def certificate39 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs001.envelope39,(8647/4000),(148832813/1000000000),(135140731992612482481/125000000000000000),(71829109/31250000),(8/5),(316199983/250000000),0,(563222762865797403/500000000000000000),(1794941850755013/500000000000000000)⟩
theorem valid39 : certificate39.Valid := by
  refine ⟨MajorityCertificates.Inputs001.inputs_valid39,?_⟩
  decide +kernel
theorem sound39 : certificate39.Sound :=
  rat_witness_certificate_sound certificate39 valid39 MajorityCertificates.Inputs001.envelope_sound39

def certificates : List RatWitnessCertificate := [certificate20,certificate21,certificate22,certificate23,certificate24,certificate25,certificate26,certificate27,certificate28,certificate29,certificate30,certificate31,certificate32,certificate33,certificate34,certificate35,certificate36,certificate37,certificate38,certificate39]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound20,List.forall_mem_cons.mpr ⟨sound21,List.forall_mem_cons.mpr ⟨sound22,List.forall_mem_cons.mpr ⟨sound23,List.forall_mem_cons.mpr ⟨sound24,List.forall_mem_cons.mpr ⟨sound25,List.forall_mem_cons.mpr ⟨sound26,List.forall_mem_cons.mpr ⟨sound27,List.forall_mem_cons.mpr ⟨sound28,List.forall_mem_cons.mpr ⟨sound29,List.forall_mem_cons.mpr ⟨sound30,List.forall_mem_cons.mpr ⟨sound31,List.forall_mem_cons.mpr ⟨sound32,List.forall_mem_cons.mpr ⟨sound33,List.forall_mem_cons.mpr ⟨sound34,List.forall_mem_cons.mpr ⟨sound35,List.forall_mem_cons.mpr ⟨sound36,List.forall_mem_cons.mpr ⟨sound37,List.forall_mem_cons.mpr ⟨sound38,List.forall_mem_cons.mpr ⟨sound39,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch001
