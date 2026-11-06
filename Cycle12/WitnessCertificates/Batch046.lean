import Cycle12.RationalWitnessCertificate
import Cycle12.MajorityCertificates.Inputs046

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Cycle12.WitnessCertificates.Batch046

def certificate920 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs046.envelope920,(47/20),(1757/10000),(46277353761204040216509/1000000000000000000),(46576943/25000000),32,(464786207/1000000000),0,1,(12681591094399/125000000000000000)⟩
theorem valid920 : certificate920.Valid := by
  refine ⟨MajorityCertificates.Inputs046.inputs_valid920,?_⟩
  decide +kernel
theorem sound920 : certificate920.Sound :=
  rat_witness_certificate_sound certificate920 valid920 MajorityCertificates.Inputs046.envelope_sound920

def certificate921 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs046.envelope921,(47/20),(1757/10000),(46277353761204040216509/1000000000000000000),(1757733543/1000000000),32,(758396077/500000000),0,(14062887933003543/12500000000000000),(51865006253091/250000000000000000)⟩
theorem valid921 : certificate921.Valid := by
  refine ⟨MajorityCertificates.Inputs046.inputs_valid921,?_⟩
  decide +kernel
theorem sound921 : certificate921.Sound :=
  rat_witness_certificate_sound certificate921 valid921 MajorityCertificates.Inputs046.envelope_sound921

def certificate922 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs046.envelope922,(47/20),(3/10),(46277353761204040216509/1000000000000000000),(361458593/200000000),32,(1007/1000),(365654784117214133/1000000000000000000),1,(1118147109755953/250000000000000000)⟩
theorem valid922 : certificate922.Valid := by
  refine ⟨MajorityCertificates.Inputs046.inputs_valid922,?_⟩
  decide +kernel
theorem sound922 : certificate922.Sound :=
  rat_witness_certificate_sound certificate922 valid922 MajorityCertificates.Inputs046.envelope_sound922

def certificate923 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs046.envelope923,(47/20),(883/5000),(5510348923315457000307/125000000000000000),(373274619/200000000),32,(233507273/500000000),0,1,(106680392684819/1000000000000000000)⟩
theorem valid923 : certificate923.Valid := by
  refine ⟨MajorityCertificates.Inputs046.inputs_valid923,?_⟩
  decide +kernel
theorem sound923 : certificate923.Sound :=
  rat_witness_certificate_sound certificate923 valid923 MajorityCertificates.Inputs046.envelope_sound923

def certificate924 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs046.envelope924,(47/20),(883/5000),(5510348923315457000307/125000000000000000),(1756725623/1000000000),32,(1517003067/1000000000),0,(1125032579664674973/1000000000000000000),(429626199721/1953125000000000)⟩
theorem valid924 : certificate924.Valid := by
  refine ⟨MajorityCertificates.Inputs046.inputs_valid924,?_⟩
  decide +kernel
theorem sound924 : certificate924.Sound :=
  rat_witness_certificate_sound certificate924 valid924 MajorityCertificates.Inputs046.envelope_sound924

def certificate925 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs046.envelope925,(47/20),(3/10),(5510348923315457000307/125000000000000000),(181462127/100000000),32,(1007/1000),(182451074331031943/500000000000000000),1,(447258843902381/100000000000000000)⟩
theorem valid925 : certificate925.Valid := by
  refine ⟨MajorityCertificates.Inputs046.inputs_valid925,?_⟩
  decide +kernel
theorem sound925 : certificate925.Sound :=
  rat_witness_certificate_sound certificate925 valid925 MajorityCertificates.Inputs046.envelope_sound925

def certificate926 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs046.envelope926,(47/20),(71/400),(432576998846285068239/10000000000000000),(1870300189/1000000000),32,(234589719/500000000),0,1,(10850964500599/100000000000000000)⟩
theorem valid926 : certificate926.Valid := by
  refine ⟨MajorityCertificates.Inputs046.inputs_valid926,?_⟩
  decide +kernel
theorem sound926 : certificate926.Sound :=
  rat_witness_certificate_sound certificate926 valid926 MajorityCertificates.Inputs046.envelope_sound926

def certificate927 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs046.envelope927,(47/20),(71/400),(432576998846285068239/10000000000000000),(439218317/250000000),32,(18945953/12500000),0,(1125033201099045139/1000000000000000000),(112986104781673/500000000000000000)⟩
theorem valid927 : certificate927.Valid := by
  refine ⟨MajorityCertificates.Inputs046.inputs_valid927,?_⟩
  decide +kernel
theorem sound927 : certificate927.Sound :=
  rat_witness_certificate_sound certificate927 valid927 MajorityCertificates.Inputs046.envelope_sound927

def certificate928 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs046.envelope928,(47/20),(3/10),(432576998846285068239/10000000000000000),(455757911/250000000),32,(1007/1000),(364053448760435101/1000000000000000000),1,(4472588439023811/1000000000000000000)⟩
theorem valid928 : certificate928.Valid := by
  refine ⟨MajorityCertificates.Inputs046.inputs_valid928,?_⟩
  decide +kernel
theorem sound928 : certificate928.Sound :=
  rat_witness_certificate_sound certificate928 valid928 MajorityCertificates.Inputs046.envelope_sound928

def certificate929 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs046.envelope929,(47/20),(3559/20000),(21132766810810694409729/500000000000000000),(233991851/125000000),32,(235150117/500000000),0,1,(55563559439731/500000000000000000)⟩
theorem valid929 : certificate929.Valid := by
  refine ⟨MajorityCertificates.Inputs046.inputs_valid929,?_⟩
  decide +kernel
theorem sound929 : certificate929.Sound :=
  rat_witness_certificate_sound certificate929 valid929 MajorityCertificates.Inputs046.envelope_sound929

def certificate930 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs046.envelope930,(47/20),(3559/20000),(21132766810810694409729/500000000000000000),(1756511871/1000000000),32,(1515619251/1000000000),0,(112503398049969183/100000000000000000),(46491201274331/200000000000000000)⟩
theorem valid930 : certificate930.Valid := by
  refine ⟨MajorityCertificates.Inputs046.inputs_valid930,?_⟩
  decide +kernel
theorem sound930 : certificate930.Sound :=
  rat_witness_certificate_sound certificate930 valid930 MajorityCertificates.Inputs046.envelope_sound930

def certificate931 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs046.envelope931,(47/20),(3/10),(21132766810810694409729/500000000000000000),(913372409/500000000),32,(1007/1000),(363683995225065569/1000000000000000000),1,(447258843902381/100000000000000000)⟩
theorem valid931 : certificate931.Valid := by
  refine ⟨MajorityCertificates.Inputs046.inputs_valid931,?_⟩
  decide +kernel
theorem sound931 : certificate931.Sound :=
  rat_witness_certificate_sound certificate931 valid931 MajorityCertificates.Inputs046.envelope_sound931

def certificate932 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs046.envelope932,(47/20),(223/1250),(8040784305062615797027/200000000000000000),(1872868331/1000000000),32,(471498731/1000000000),0,1,(117255197997839/1000000000000000000)⟩
theorem valid932 : certificate932.Valid := by
  refine ⟨MajorityCertificates.Inputs046.inputs_valid932,?_⟩
  decide +kernel
theorem sound932 : certificate932.Sound :=
  rat_witness_certificate_sound certificate932 valid932 MajorityCertificates.Inputs046.envelope_sound932

def certificate933 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs046.envelope933,(47/20),(223/1250),(8040784305062615797027/200000000000000000),(43890943/25000000),32,(1516340669/1000000000),0,(1125035723024716883/1000000000000000000),(61470702495217/250000000000000000)⟩
theorem valid933 : certificate933.Valid := by
  refine ⟨MajorityCertificates.Inputs046.inputs_valid933,?_⟩
  decide +kernel
theorem sound933 : certificate933.Sound :=
  rat_witness_certificate_sound certificate933 valid933 MajorityCertificates.Inputs046.envelope_sound933

def certificate934 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs046.envelope934,(47/20),(61/200),(8040784305062615797027/200000000000000000),(908359933/500000000),32,(1007/1000),(370215839566162283/1000000000000000000),1,(4472588439023811/1000000000000000000)⟩
theorem valid934 : certificate934.Valid := by
  refine ⟨MajorityCertificates.Inputs046.inputs_valid934,?_⟩
  decide +kernel
theorem sound934 : certificate934.Sound :=
  rat_witness_certificate_sound certificate934 valid934 MajorityCertificates.Inputs046.envelope_sound934

def certificate935 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs046.envelope935,(47/20),(1793/10000),(39518323636388087884083/1000000000000000000),(938440103/500000000),32,(118416709/250000000),0,1,(119068842598949/1000000000000000000)⟩
theorem valid935 : certificate935.Valid := by
  refine ⟨MajorityCertificates.Inputs046.inputs_valid935,?_⟩
  decide +kernel
theorem sound935 : certificate935.Sound :=
  rat_witness_certificate_sound certificate935 valid935 MajorityCertificates.Inputs046.envelope_sound935

def certificate936 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs046.envelope936,(47/20),(1793/10000),(39518323636388087884083/1000000000000000000),(1756434903/1000000000),32,(378563057/250000000),0,(1125036342794065619/1000000000000000000),(251541292107797/1000000000000000000)⟩
theorem valid936 : certificate936.Valid := by
  refine ⟨MajorityCertificates.Inputs046.inputs_valid936,?_⟩
  decide +kernel
theorem sound936 : certificate936.Sound :=
  rat_witness_certificate_sound certificate936 valid936 MajorityCertificates.Inputs046.envelope_sound936

def certificate937 : RatWitnessCertificate := ⟨.localCut,MajorityCertificates.Inputs046.envelope937,(47/20),(61/200),(39518323636388087884083/1000000000000000000),(73006137/40000000),32,(1007/1000),(73873117662360651/200000000000000000),1,(447258843902381/100000000000000000)⟩
theorem valid937 : certificate937.Valid := by
  refine ⟨MajorityCertificates.Inputs046.inputs_valid937,?_⟩
  decide +kernel
theorem sound937 : certificate937.Sound :=
  rat_witness_certificate_sound certificate937 valid937 MajorityCertificates.Inputs046.envelope_sound937

def certificate938 : RatWitnessCertificate := ⟨.globalCut,MajorityCertificates.Inputs046.envelope938,(47/20),(719/4000),(19336270263458644086213/500000000000000000),(234817481/125000000),32,(1899163/4000000),0,1,(15219160670537/125000000000000000)⟩
theorem valid938 : certificate938.Valid := by
  refine ⟨MajorityCertificates.Inputs046.inputs_valid938,?_⟩
  decide +kernel
theorem sound938 : certificate938.Sound :=
  rat_witness_certificate_sound certificate938 valid938 MajorityCertificates.Inputs046.envelope_sound938

def certificate939 : RatWitnessCertificate := ⟨.anchor,MajorityCertificates.Inputs046.envelope939,(47/20),(719/4000),(19336270263458644086213/500000000000000000),(43871871/25000000),32,(1515655151/1000000000),0,(281259284411286263/250000000000000000),(259980275841269/1000000000000000000)⟩
theorem valid939 : certificate939.Valid := by
  refine ⟨MajorityCertificates.Inputs046.inputs_valid939,?_⟩
  decide +kernel
theorem sound939 : certificate939.Sound :=
  rat_witness_certificate_sound certificate939 valid939 MajorityCertificates.Inputs046.envelope_sound939

def certificates : List RatWitnessCertificate := [certificate920,certificate921,certificate922,certificate923,certificate924,certificate925,certificate926,certificate927,certificate928,certificate929,certificate930,certificate931,certificate932,certificate933,certificate934,certificate935,certificate936,certificate937,certificate938,certificate939]
theorem certificates_sound : ∀ c∈certificates, c.Sound := by
  unfold certificates
  exact List.forall_mem_cons.mpr ⟨sound920,List.forall_mem_cons.mpr ⟨sound921,List.forall_mem_cons.mpr ⟨sound922,List.forall_mem_cons.mpr ⟨sound923,List.forall_mem_cons.mpr ⟨sound924,List.forall_mem_cons.mpr ⟨sound925,List.forall_mem_cons.mpr ⟨sound926,List.forall_mem_cons.mpr ⟨sound927,List.forall_mem_cons.mpr ⟨sound928,List.forall_mem_cons.mpr ⟨sound929,List.forall_mem_cons.mpr ⟨sound930,List.forall_mem_cons.mpr ⟨sound931,List.forall_mem_cons.mpr ⟨sound932,List.forall_mem_cons.mpr ⟨sound933,List.forall_mem_cons.mpr ⟨sound934,List.forall_mem_cons.mpr ⟨sound935,List.forall_mem_cons.mpr ⟨sound936,List.forall_mem_cons.mpr ⟨sound937,List.forall_mem_cons.mpr ⟨sound938,List.forall_mem_cons.mpr ⟨sound939,List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
end Cycle12.WitnessCertificates.Batch046
